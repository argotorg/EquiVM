import Examples.Precompiles.Modexp.WordLoopBridge

/-!
# Caller-visible specification for the completed ModExp edge path

This is a direct bytecode theorem: there is no Solm refinement layer.  It states the pure successful
projection of the trusted ModExp runner and the exact OOG threshold at the `Θ`-observable interface.
-/

open Ethereum Ethereum.EVM Reasoning.Reach

namespace Modexp

def smallModulusEnsures (ctx : BytecodeContext) (result : BytecodeResult) : Prop :=
  ExactGasPost ctx (Model.output ctx.executionEnv.calldata) smallModulusGasCost result

theorem smallModulusBytecodeSpec :
    BytecodeSpec runtimeBytecode smallModulusAccepts smallModulusEnsures := by
  simpa [smallModulusEnsures] using
    (ExactGasSpec.ofRDxRet (code := runtimeBytecode)
      (accepts := smallModulusAccepts)
      (output := fun ctx => Model.output ctx.executionEnv.calldata)
      (gasCost := fun _ => smallModulusGasCost)
      (fun ctx hcode haccepts => by
        rcases haccepts with ⟨hvalue, hb, he, hm, hmod⟩
        exact smallModulusModelExactGas
          (cA := ctx.createdAccounts) (gh := ctx.genesisBlockHeader) (bl := ctx.blocks)
          (σ := ctx.accountMap) (σ₀ := ctx.originalAccountMap) (A := ctx.substate)
          (I := ctx.executionEnv) (g := ctx.gas)
          hcode hvalue hb he hm hmod))

/-- The complete stack-only path, stated using the trusted parser rather than implementation
stack words. -/
def wordAccepts (ctx : BytecodeContext) : Prop :=
  ctx.executionEnv.weiValue = ⟨0⟩ ∧ wordSized ctx.executionEnv.calldata

def wordEnsures (ctx : BytecodeContext) (result : BytecodeResult) : Prop :=
  ExactGasPost ctx (Model.output ctx.executionEnv.calldata)
    (wordGasCost ctx.executionEnv) result

/-- Every input whose three operands fit one EVM word returns the trusted ModExp result, with the
exact executable gas expression `wordGasCost`.  This covers both the modulus-zero/one edge block
and every iteration of the nontrivial square-and-multiply loop. -/
theorem wordBytecodeSpec :
    BytecodeSpec runtimeBytecode wordAccepts wordEnsures := by
  simpa [wordEnsures] using
    (ExactGasSpec.ofRDxRet (code := runtimeBytecode)
      (accepts := wordAccepts)
      (output := fun ctx => Model.output ctx.executionEnv.calldata)
      (gasCost := fun ctx => wordGasCost ctx.executionEnv)
      (fun ctx hcode haccepts => by
        rcases haccepts with ⟨hvalue, hsized⟩
        rcases hsized with ⟨hb, he, hm⟩
        apply wordModelExactGas
          (cA := ctx.createdAccounts) (gh := ctx.genesisBlockHeader) (bl := ctx.blocks)
          (σ := ctx.accountMap) (σ₀ := ctx.originalAccountMap) (A := ctx.substate)
          (I := ctx.executionEnv) (g := ctx.gas)
          hcode hvalue
        · simpa using hb
        · simpa using he
        · simpa using hm))

end Modexp
