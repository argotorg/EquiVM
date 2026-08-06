import Examples.Precompiles.Blake2f.Spec

/-!
# BLAKE2F bytecode proof interface

This file packages the proof obligations needed to close the BLAKE2F experiment.  It contains no
Solm refinement: the final theorem is directly about bytecode execution at the caller-visible
`Θ`/`Ξ` projection used by `Reasoning.Bytecode`.
-/

open Ethereum Ethereum.EVM Reasoning.Reach

namespace Blake2f

/-- Successful valid-input trace obligation for a candidate exact bytecode gas term. -/
abbrev ValidTrace (gasCost : BytecodeContext → Nat) : Prop :=
  ∀ ctx : BytecodeContext,
    ctx.executionEnv.code = runtimeBytecode →
    accepts ctx →
    valid ctx →
    RDxRet runtimeBytecode ctx.gas ctx.initialState
      (ctx.createdAccounts, ctx.accountMap)
      (output ctx) (gasCost ctx)

/-- Invalid-input trace obligation.  The exact invalid-path halt kind and threshold are not public:
`Θ` observes any exceptional `Ξ` result as the same failed call with empty output and zero gas. -/
abbrev InvalidTrace : Prop :=
  ∀ ctx : BytecodeContext,
    ctx.executionEnv.code = runtimeBytecode →
    accepts ctx →
    ¬ valid ctx →
    ∃ exception errorThreshold,
      RDxErr runtimeBytecode ctx.gas ctx.initialState exception errorThreshold

end Blake2f
